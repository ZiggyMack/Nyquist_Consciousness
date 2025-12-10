# Fleet Maintenance Guide

**Purpose:** Keep the S7 ARMADA fleet operational as providers update/retire models.

---

## Current Fleet Status (2025-12-10)

| Provider | Verified | Ghost | Rate Limited | Total |
|----------|----------|-------|--------------|-------|
| Claude   | 7        | 0     | 0            | 7     |
| GPT (standard) | 7  | 0     | 0            | 7     |
| GPT (max_completion_tokens) | 7 | 0 | 0     | 7     |
| Gemini   | 3        | 0     | 5            | 8     |
| Grok (xAI) | 10     | 0     | 0            | 10    |
| Together.ai | 15    | 5     | 0            | 20    |
| **TOTAL**| **49**   | **5** | **5**        | **59** |

**Operational Ships**: 54 (49 verified + 5 rate-limited that may work)

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

---

## Maintenance Workflow

### 1. Monthly Calibration Check

Run the calibration to detect new ghost ships:

```powershell
cd S7_ARMADA/1_CALIBRATION
py run_calibrate_parallel.py
```

This tests all ships and updates the manifest.

### 2. Rescue Ghost Ships

When ships fail due to API parameter issues:

```powershell
cd S7_ARMADA/1_CALIBRATION
py rescue_ghost_ships.py
```

Results saved to `GHOST_SHIP_RESCUE_RESULTS.json`

### 3. Add New Models

When providers release new models:

1. Check official model lists:
   - **Claude:** https://docs.anthropic.com/en/docs/about-claude/models
   - **OpenAI:** https://platform.openai.com/docs/models
   - **Google:** https://ai.google.dev/gemini-api/docs/models/gemini

2. Add to `run_calibrate_parallel.py` in the `FLEET_CONFIG`

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

---

## Manifest Location

```
S7_ARMADA/
  0_results/
    manifests/
      VERIFIED_FLEET_MANIFEST.json  <- Current fleet status
  1_CALIBRATION/
    GHOST_SHIP_RESCUE_RESULTS.json  <- Last rescue mission results
```

---

## Provider Update Schedule

- **OpenAI:** Models typically updated quarterly, old versions deprecated ~6 months after successor
- **Google:** Experimental models rotate frequently, stable models more permanent
- **Anthropic:** Model versions persist longer, clear deprecation notices

**Recommendation:** Run calibration monthly, or after any major provider announcement.

---

Last Updated: 2025-12-10
