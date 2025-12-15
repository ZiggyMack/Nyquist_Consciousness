# Fleet Maintenance Guide

**Purpose:** Keep the S7 ARMADA fleet operational as providers update/retire models.

**Version:** 2.0 (December 2025)

---

## Current Fleet Status (2025-12-14)

| Provider | Operational | Ghost | Rate Limited | Total |
|----------|-------------|-------|--------------|-------|
| Claude (Anthropic) | 7 | 0 | 0 | 7 |
| GPT (OpenAI) | 14 | 0 | 0 | 14 |
| Gemini (Google) | 3 | 0 | 5 | 8 |
| Grok (xAI) | 9 | 0 | 0 | 9 |
| Together.ai | 16 | 0 | 0 | 16 |
| **TOTAL** | **49** | **0** | **5** | **54** |

**FULL ARMADA**: 49 operational ships (91% of fleet)

For complete fleet roster with model IDs, see [ARMADA_MAP.md](../../../docs/maps/ARMADA_MAP.md).

---

## Calibration Scripts

All calibration scripts are in `S7_ARMADA/1_CALIBRATION/`:

### 1. `run_calibrate.py` - Basic VALIS Handshake

The original calibration script. Tests 10 representative ships (1 per lineage).

```powershell
cd S7_ARMADA/1_CALIBRATION
py run_calibrate.py
```

**What it does:**

- Sends VALIS handshake to each ship
- Tests basic connectivity
- Records fleet intentions

**Output:** `../0_results/calibration/S7_calibration_{timestamp}.json`

### 2. `run_calibrate_parallel.py` - Full Fleet Calibration

The comprehensive calibration script with parallel execution.

```powershell
# Quick mode: 1 model per provider (bandwidth test)
py run_calibrate_parallel.py --quick

# Full mode: ALL models (ghost ship detection)
py run_calibrate_parallel.py --full

# Bandwidth mode: Test concurrency scaling
py run_calibrate_parallel.py --bandwidth
```

**Features:**

- **KeyPool**: Rotates through multiple API keys per provider (up to 10 each)
- **QUICK_FLEET**: Fast test with 1 ship per provider (5 total)
- **FULL_ARMADA**: All 49 operational ships across 5 providers
- **Parallel execution**: ThreadPoolExecutor with configurable workers
- **Ghost ship detection**: Identifies models that fail with specific errors

**Output:**

- Console: Real-time status per ship
- File: `../0_results/calibration/S7_calibration_{timestamp}.json`

### 3. `rescue_ghost_ships.py` - Ghost Ship Recovery

Attempts to rescue failed ships using alternative API parameters.

```powershell
py rescue_ghost_ships.py
```

**Common rescue strategies:**

| Error | Rescue Strategy |
|-------|-----------------|
| `max_tokens not supported` | Use `max_completion_tokens` instead |
| `404 model not found` | Check provider docs for renamed model |
| `v1/completions endpoint` | Switch from chat to completions API |

**Output:** `GHOST_SHIP_RESCUE_RESULTS.json`

---

## Key API Differences

### GPT Models Requiring `max_completion_tokens`

These models do NOT support `max_tokens`:

- `gpt-5.1`, `gpt-5`, `gpt-5-mini`, `gpt-5-nano`
- `o4-mini`, `o3`, `o3-mini`, `o1`

**Fix:** Use `max_completion_tokens=1000` instead of `max_tokens=1000`

### GPT Models Requiring Different Endpoints

- `gpt-5.1-codex` - needs `v1/completions` (not chat)
- `gpt-5-pro` - needs `v1/responses` (specialized)

These are currently ghost ships until we add endpoint switching.

### Gemini Rate Limiting

Several Gemini models are rate-limited on free tier:

- `gemini-3-pro`, `gemini-2.5-pro`
- `gemini-2.0-flash-lite`, `gemini-2.0-flash-thinking`
- `gemma-3n`

**Workaround:** Add delays between requests or use paid tier.

---

## Maintenance Workflow

### 1. Monthly Calibration Check

```powershell
cd S7_ARMADA/1_CALIBRATION
py run_calibrate_parallel.py --full
```

This tests all ships and identifies:

- New ghost ships (API changes)
- Rate limit changes
- Model retirements

### 2. Rescue Ghost Ships

```powershell
py rescue_ghost_ships.py
```

Review results and update fleet manifest.

### 3. Add New Models

When providers release new models:

1. Check official model lists:
   - **Claude:** https://docs.anthropic.com/en/docs/about-claude/models
   - **OpenAI:** https://platform.openai.com/docs/models
   - **Google:** https://ai.google.dev/gemini-api/docs/models/gemini
   - **xAI:** https://docs.x.ai/docs/models
   - **Together.ai:** https://api.together.xyz/models

2. Add to `run_calibrate_parallel.py` in the `FULL_ARMADA` config

3. Run calibration to verify

4. Update `VERIFIED_FLEET_MANIFEST.json`

---

## Common Ghost Ship Causes

| Error Message | Cause | Fix |
|--------------|-------|-----|
| `max_tokens not supported` | Model uses new API | Use `max_completion_tokens` |
| `404 model not found` | Model retired/renamed | Check official docs for new name |
| `v1/completions endpoint` | Codex-style model | Use completions instead of chat |
| `v1/responses endpoint` | Pro/specialized model | Use responses API |
| `rate_limit_exceeded` | Too many requests | Add delays or use key rotation |

---

## File Locations

```text
S7_ARMADA/
  0_results/
    calibration/
      S7_calibration_{timestamp}.json  <- Calibration results
    manifests/
      VERIFIED_FLEET_MANIFEST.json     <- Current fleet status
  1_CALIBRATION/
    run_calibrate.py                   <- Basic 10-ship test
    run_calibrate_parallel.py          <- Full fleet parallel test
    rescue_ghost_ships.py              <- Ghost ship recovery
    GHOST_SHIP_RESCUE_RESULTS.json     <- Last rescue mission results
```

---

## Provider Update Schedule

- **OpenAI:** Models typically updated quarterly, old versions deprecated ~6 months after successor
- **Google:** Experimental models rotate frequently, stable models more permanent
- **Anthropic:** Model versions persist longer, clear deprecation notices
- **xAI:** Rapid updates, check frequently
- **Together.ai:** Depends on upstream model providers

**Recommendation:** Run calibration monthly, or after any major provider announcement.

---

## Scaling the Fleet

### Adding More API Keys

The KeyPool in `run_calibrate_parallel.py` supports multiple keys per provider:

```bash
# In .env file
ANTHROPIC_API_KEY_1=sk-ant-...
ANTHROPIC_API_KEY_2=sk-ant-...
# ... up to 10 per provider
```

This enables:

- Higher concurrency without rate limits
- Failover if one key hits limits
- Load distribution across keys

### Adjusting Parallelism

Edit `MAX_WORKERS` in `run_calibrate_parallel.py`:

```python
MAX_WORKERS = {
    "anthropic": 3,  # Conservative for rate limits
    "openai": 5,
    "google": 2,     # Rate-limited
    "xai": 5,
    "together": 5,
}
```

---

## Related Documents

- [0_RUN_METHODOLOGY.md](0_RUN_METHODOLOGY.md) - Run design checklist
- [2_PROBE_SPEC.md](2_PROBE_SPEC.md) - SONAR probe curriculum
- [ARMADA_MAP.md](../../../docs/maps/ARMADA_MAP.md) - Complete fleet roster with model IDs and costs

---

*Last Updated: December 12, 2025*
